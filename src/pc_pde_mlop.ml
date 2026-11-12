(* ========================================================================= *)
(* Unit pc_pde_mlop (the linear theory on M, first part): the local operator *)
(* tr_K Hess_H V.  Jets of pde_ltrhess K H V for an arbitrary smooth matrix  *)
(* field V, linearity, the pde_lop0 form with explicit coefficients,         *)
(* naturality under diffeomorphisms, and the chart form of pde_mlin_sol.     *)
(* ========================================================================= *)

needs "src/pc_pde_texist.ml";;
needs "src/pc_pde_mloc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The jet formula of pc_pde_rdt_symbol for the Hessian of an arbitrary      *)
(* smooth matrix field V (not only of metric fields): only the smoothness of *)
(* V on the open set is used.  The second argument K of pde_ltrhess enters   *)
(* only through matrix_inv(K y).                                             *)
(* ========================================================================= *)

let PDE_ML_G_ENTRY_SMOOTH = prove
 (`!U (V:real^N->real^N^N) i j.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V)
     ==> smooth_map_on U (\z. lift((V z)$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift(((V:real^N->real^N^N) z)$i$j)) =
                (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
                ((vectorize:real^N^N->real^(N,N)finite_prod) o V)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY]);;

let PDE_ML_MDERIV_ENTRY_SMOOTH = prove
 (`!U (V:real^N->real^N^N) w i j.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V)
     ==> smooth_map_on U (\z. lift((mderiv V z w)$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((mderiv (V:real^N->real^N^N) z w)$i$j)) =
                (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
                ((vectorize:real^N^N->real^(N,N)finite_prod) o (\z. mderiv V z w))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  MATCH_MP_TAC LRG_SMOOTH_MDERIV THEN ASM_REWRITE_TAC[]);;

let PDE_ML_JG_PARTIAL = prove
 (`!U (V:real^N->real^N^N) y c a b.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     y IN U /\ 1 <= c /\ c <= dimindex(:N)
     ==> partial_derivative c (\z. lift((V z)$a$b)) y = lift(pde_jd1 V y c a b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`; `[]:num list`; `a:num`; `b:num`]
                JP_GOOD_VAR) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[jp_good] THEN DISCH_THEN(MP_TAC o SPECL [`c:num`; `y:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[jp_dx; jp_eval; iterated_partial; o_THM; MATRIFY_VECTORIZE;
                  PDE_MDERIV_ENTRY_ITERATED; pde_jd1] THEN
  REWRITE_TAC[ETA_AX]);;

let PDE_ML_JD1_PARTIAL = prove
 (`!U (V:real^N->real^N^N) y c e a b.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     y IN U /\ 1 <= c /\ c <= dimindex(:N)
     ==> partial_derivative c (\z. lift((mderiv V z (basis e))$a$b)) y =
         lift(pde_jd2 V y c e a b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`; `[e:num]`; `a:num`; `b:num`]
                JP_GOOD_VAR) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[jp_good] THEN DISCH_THEN(MP_TAC o SPECL [`c:num`; `y:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[jp_dx; GSYM PDE_MDERIV_BASIS_ENTRY] THEN
  REWRITE_TAC[jp_eval; pde_jd2; ETA_AX]);;

let PDE_ML_LMETRIC2_FIELD = prove
 (`!U (V:real^N->real^N^N).
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V)
     ==> ltensor_field 2 U (lmetric2 V) /\
         (!u. smooth_map_on U (\y. lift(lmetric2 V y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ltensor_field; lmetric2] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BINOP_TAC THEN TRY AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[ARITH] THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
      SUBGOAL_THEN
       `(\v. lift((u:num->real^N) 1 dot ((V:real^N->real^N^N) y ** v))) =
        (\v. (\x. lift(u 1 dot x)) ((\v. V y ** v) v))`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
      REWRITE_TAC[LINEAR_LIFT_DOT; MATRIX_VECTOR_MUL_LINEAR]];
    GEN_TAC THEN REWRITE_TAC[lmetric2] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]]);;

let PDE_ML_LNABLA2_FIELD = prove
 (`!U (V:real^N->real^N^N) H.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H
     ==> ltensor_field 3 U (lnabla 2 H (lmetric2 V)) /\
         (!u. smooth_map_on U (\y. lift(lnabla 2 H (lmetric2 V) y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `H:real^N->real^N^N`; `lmetric2 (V:real^N->real^N^N)`]
                LNABLA_TENSOR_FIELD) THEN
  ASM_SIMP_TAC[PDE_ML_LMETRIC2_FIELD; ARITH_RULE `2 + 1 = 3`]);;

let PDE_ML_LNABLA2_BASIS = prove
 (`!U (V:real^N->real^N^N) H z (u:num->real^N) a b p.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H /\ z IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= p /\ p <= dimindex(:N) /\
     u 1 = basis a /\ u 2 = basis b /\ u 3 = basis p
     ==> lnabla 2 H (lmetric2 V) z u =
         pde_jsl (dimindex(:N)) (pde_jg V z) (pde_jd1 V z) (pde_jhc H z) a b p`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LRG_LNABLA_EQ; lmetric2; SUM_2; ARITH_RULE `2 + 1 = 3`] THEN
  REWRITE_TAC[ARITH_RULE `~(2 = 1) /\ ~(1 = 2)`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (V:real^N->real^N^N))
                differentiable (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->real^N^N`; `z:real^N`; `basis a:real^N`; `basis b:real^N`]
                LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN
   `christoffel (H:real^N->real^N^N) z (basis p) (basis a) dot
      ((V:real^N->real^N^N) z ** basis b) =
    sum(1..dimindex(:N)) (\m. pde_jhc H z m p a * pde_jg V z m b) /\
    basis a dot (V z ** christoffel H z (basis p) (basis b)) =
    sum(1..dimindex(:N)) (\m. pde_jg V z a m * pde_jhc H z m p b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[dot; pde_jhc; pde_jg] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DOT_BASIS];
      ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[dot; pde_jhc; pde_jg]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pde_jsl] THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[pde_jd1] THEN REAL_ARITH_TAC);;

let PDE_ML_JSL_PARTIAL = prove
 (`!U (V:real^N->real^N^N) H y a b p q.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> drop(partial_derivative q
                (\x. lift(pde_jsl (dimindex(:N)) (pde_jg V x) (pde_jd1 V x) (pde_jhc H x)
                                  a b p)) y) =
         pde_jdsl (dimindex(:N)) (pde_jg V y) (pde_jd1 V y) (pde_jd2 V y)
                  (pde_jhc H y) (pde_jhdc H y) a b p q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!f:real^N->real^1. smooth_map_on U f ==> f differentiable (at y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`; `y:real^N`] PDE_ML_JD1_PARTIAL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`; `y:real^N`] PDE_ML_JG_PARTIAL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `H:real^N->real^N^N`; `y:real^N`] PDE_HCHR_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[pde_jsl; pde_jg; pde_jd1; pde_jhc] THEN
  PDE_ASM_DEEP_SIMP_TAC[PDE_RD_SUB; PDE_RD_MUL; PDE_RD_SUM; FINITE_NUMSEG; IN_NUMSEG; LIFT_DROP;
               LRG_SMOOTH_LIFT_MUL_REAL; LRG_SMOOTH_LIFT_SUM_REAL;
               PDE_SMOOTH_LIFT_SUB_REAL; PDE_ML_MDERIV_ENTRY_SMOOTH; PDE_ML_G_ENTRY_SMOOTH;
               PDE_SMOOTH_CHR_ENTRY] THEN
  REWRITE_TAC[pde_jdsl; pde_jg; pde_jd1; pde_jhc] THEN
  BINOP_TAC THENL [BINOP_TAC THENL [REWRITE_TAC[]; ALL_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The jet formula for tr_K Hess_H V (PDE_ML_TRHESS_JET) and the linearity   *)
(* of the jet polynomial pde_jtrhess in the jets (g, d1, d2) of V.           *)
(* ========================================================================= *)

let PDE_ML_HESS4_JET = prove
 (`!U (V:real^N->real^N^N) H y a b p q.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> lnabla_iter 2 2 H (lmetric2 V) y
           (\m. if m = 1 then basis a else if m = 2 then basis b
                else if m = 3 then basis p else basis q) =
         pde_jhess (dimindex(:N)) (pde_jg V y) (pde_jd1 V y) (pde_jd2 V y)
                   (pde_jhc H y) (pde_jhdc H y) a b p q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = lnabla 2 (H:real^N->real^N^N) (lmetric2 (V:real^N->real^N^N))` THEN
  ABBREV_TAC `u4 = \m. if m = 1 then basis a else if m = 2 then basis b
                       else if m = 3 then basis p else basis q:real^N` THEN
  SUBGOAL_THEN `(u4:num->real^N) 1 = basis a /\ u4 2 = basis b /\ u4 3 = basis p /\
                u4 4 = basis q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u4" THEN CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`; `H:real^N->real^N^N`]
                PDE_ML_LNABLA2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[PDE_LNABLA_ITER_2; ARITH_RULE `2 + 1 = 3`] THEN
  ASM_REWRITE_TAC[LRG_LNABLA_EQ; ARITH_RULE `3 + 1 = 4`; SUM_3] THEN
  REWRITE_TAC[GSYM partial_derivative] THEN
  SUBGOAL_THEN
   `drop(partial_derivative q (\x. lift((S:real^N->(num->real^N)->real) x u4)) y) =
    pde_jdsl (dimindex(:N)) (pde_jg V y) (pde_jd1 V y) (pde_jd2 V y)
             (pde_jhc H y) (pde_jhdc H y) a b p q`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `drop(partial_derivative q
             (\x. lift(pde_jsl (dimindex(:N)) (pde_jg (V:real^N->real^N^N) x) (pde_jd1 V x)
                               (pde_jhc (H:real^N->real^N^N) x) a b p)) y)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      EXPAND_TAC "S" THEN MATCH_MP_TAC PDE_ML_LNABLA2_BASIS THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_ML_JSL_PARTIAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i (v:real^N). 1 <= i /\ i <= 3
        ==> (S:real^N->(num->real^N)->real) y (\j. if j = i then v else u4 j) =
            sum(1..dimindex(:N)) (\r. v$r * S y (\j. if j = i then basis r else u4 j))`
  (LABEL_TAC "SLOT") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SLOT_EXPAND THEN
    UNDISCH_TAC `ltensor_field 3 U (S:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. 1 <= r /\ r <= dimindex(:N)
        ==> (S:real^N->(num->real^N)->real) y (\j. if j = 1 then basis r else u4 j) =
            pde_jsl (dimindex(:N)) (pde_jg V y) (pde_jd1 V y) (pde_jhc H y) r b p /\
            S y (\j. if j = 2 then basis r else u4 j) =
            pde_jsl (dimindex(:N)) (pde_jg V y) (pde_jd1 V y) (pde_jhc H y) a r p /\
            S y (\j. if j = 3 then basis r else u4 j) =
            pde_jsl (dimindex(:N)) (pde_jg V y) (pde_jd1 V y) (pde_jhc H y) a b r`
  (LABEL_TAC "BAS") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "S" THEN MATCH_MP_TAC PDE_ML_LNABLA2_BASIS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "SLOT" (fun th ->
    ONCE_REWRITE_TAC[MATCH_MP th (ARITH_RULE `1 <= 1 /\ 1 <= 3`);
                MATCH_MP th (ARITH_RULE `1 <= 2 /\ 2 <= 3`);
                MATCH_MP th (ARITH_RULE `1 <= 3 /\ 3 <= 3`)]) THEN
  REWRITE_TAC[pde_jhess] THEN AP_TERM_TAC THEN
  BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  USE_THEN "BAS" (fun th -> REWRITE_TAC[MATCH_MP th
    (CONJ (ASSUME `1 <= r`) (ASSUME `r <= dimindex(:N)`))]) THEN
  REWRITE_TAC[pde_jhc]);;

let PDE_ML_TRHESS_JET = prove
 (`!U (K:real^N->real^N^N) H (V:real^N->real^N^N) y a b.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H /\ y IN U /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> pde_ltrhess K H V y $a$b =
         pde_jtrhess (dimindex(:N)) (pde_jg V y) (pde_jgi K y) (pde_jd1 V y) (pde_jd2 V y)
                     (pde_jhc H y) (pde_jhdc H y) a b`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[pde_ltrhess; LAMBDA_BETA] THEN
  REWRITE_TAC[pde_jtrhess] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  REWRITE_TAC[pde_jgi] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PDE_ML_HESS4_JET THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* Linearity of the jet polynomials in the jets of the field. *)

let PDE_ML_JSL_LIN = prove
 (`!n x y g1 g2 d11 d12 (hc:num->num->num->real) a b p.
     pde_jsl n (\i j. x * g1 i j + y * g2 i j) (\c i j. x * d11 c i j + y * d12 c i j)
             hc a b p =
     x * pde_jsl n g1 d11 hc a b p + y * pde_jsl n g2 d12 hc a b p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jsl] THEN
  REWRITE_TAC[REAL_ARITH `h * (x * g + y * g') = x * (h * g) + y * (h * g')`;
              REAL_ARITH `(x * g + y * g') * h = x * (g * h) + y * (g' * h)`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN REAL_ARITH_TAC);;

let PDE_ML_JDSL_LIN = prove
 (`!n x y g1 g2 d11 d12 d21 d22 (hc:num->num->num->real) (hdc:num->num->num->num->real)
    a b p q.
     pde_jdsl n (\i j. x * g1 i j + y * g2 i j) (\c i j. x * d11 c i j + y * d12 c i j)
              (\c e i j. x * d21 c e i j + y * d22 c e i j) hc hdc a b p q =
     x * pde_jdsl n g1 d11 d21 hc hdc a b p q + y * pde_jdsl n g2 d12 d22 hc hdc a b p q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jdsl] THEN
  REWRITE_TAC[REAL_ARITH `h * (x * g + y * g') = x * (h * g) + y * (h * g')`;
              REAL_ARITH `(x * g + y * g') * h = x * (g * h) + y * (g' * h)`] THEN
  REWRITE_TAC[REAL_ARITH `(x * a + y * b) + (x * c + y * d) =
                          x * (a + c) + y * (b + d)`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN REAL_ARITH_TAC);;

let PDE_ML_JHESS_LIN = prove
 (`!n x y g1 g2 d11 d12 d21 d22 (hc:num->num->num->real) (hdc:num->num->num->num->real)
    a b p q.
     pde_jhess n (\i j. x * g1 i j + y * g2 i j) (\c i j. x * d11 c i j + y * d12 c i j)
               (\c e i j. x * d21 c e i j + y * d22 c e i j) hc hdc a b p q =
     x * pde_jhess n g1 d11 d21 hc hdc a b p q + y * pde_jhess n g2 d12 d22 hc hdc a b p q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jhess; PDE_ML_JDSL_LIN; PDE_ML_JSL_LIN] THEN
  REWRITE_TAC[REAL_ARITH `h * (x * g + y * g') = x * (h * g) + y * (h * g')`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN REAL_ARITH_TAC);;

let PDE_ML_JTRHESS_LIN = prove
 (`!n x y g1 g2 (gi:num->num->real) d11 d12 d21 d22 (hc:num->num->num->real)
    (hdc:num->num->num->num->real) a b.
     pde_jtrhess n (\i j. x * g1 i j + y * g2 i j) gi
                 (\c i j. x * d11 c i j + y * d12 c i j)
                 (\c e i j. x * d21 c e i j + y * d22 c e i j) hc hdc a b =
     x * pde_jtrhess n g1 gi d11 d21 hc hdc a b + y * pde_jtrhess n g2 gi d12 d22 hc hdc a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_jtrhess; PDE_ML_JHESS_LIN] THEN
  REWRITE_TAC[REAL_ARITH `h * (x * g + y * g') = x * (h * g) + y * (h * g')`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL]);;

(* ========================================================================= *)
(* The lower-order coefficient matrices of tr_K Hess_H (pde_mlbb, pde_mlcc:  *)
(* matrices of the parts of the jet polynomial linear in the first jets and  *)
(* in the values of V), and the pde_lop0 form of the operator                *)
(* (PDE_ML_LOP0_FORM).                                                       *)
(* ========================================================================= *)

let PDE_ML_JT_G_ADD = prove
 (`!n g1 g2 (gi:num->num->real) (hc:num->num->num->real) (hdc:num->num->num->num->real)
    a b.
     pde_jtrhess n (\i j. g1 i j + g2 i j) gi (\c i j. &0) (\p q i j. &0) hc hdc a b =
     pde_jtrhess n g1 gi (\c i j. &0) (\p q i j. &0) hc hdc a b +
     pde_jtrhess n g2 gi (\c i j. &0) (\p q i j. &0) hc hdc a b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `&1`; `&1`; `g1:num->num->real`; `g2:num->num->real`;
                 `gi:num->num->real`; `\(c:num) (i:num) (j:num). &0`; `\(c:num) (i:num) (j:num). &0`;
                 `\(p:num) (q:num) (i:num) (j:num). &0`; `\(p:num) (q:num) (i:num) (j:num). &0`;
                 `hc:num->num->num->real`; `hdc:num->num->num->num->real`;
                 `a:num`; `b:num`] PDE_ML_JTRHESS_LIN) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RZERO; REAL_ADD_LID]);;

let PDE_ML_JT_G_CMUL = prove
 (`!n x g (gi:num->num->real) (hc:num->num->num->real) (hdc:num->num->num->num->real) a b.
     pde_jtrhess n (\i j. x * g i j) gi (\c i j. &0) (\p q i j. &0) hc hdc a b =
     x * pde_jtrhess n g gi (\c i j. &0) (\p q i j. &0) hc hdc a b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `x:real`; `&0`; `g:num->num->real`; `g:num->num->real`;
                 `gi:num->num->real`; `\(c:num) (i:num) (j:num). &0`; `\(c:num) (i:num) (j:num). &0`;
                 `\(p:num) (q:num) (i:num) (j:num). &0`; `\(p:num) (q:num) (i:num) (j:num). &0`;
                 `hc:num->num->num->real`; `hdc:num->num->num->num->real`;
                 `a:num`; `b:num`] PDE_ML_JTRHESS_LIN) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID]);;

let PDE_ML_JT_D_ADD = prove
 (`!n (gi:num->num->real) d11 d12 (hc:num->num->num->real) (hdc:num->num->num->num->real)
    a b.
     pde_jtrhess n (\i j. &0) gi (\c i j. d11 c i j + d12 c i j) (\p q i j. &0) hc hdc a b =
     pde_jtrhess n (\i j. &0) gi d11 (\p q i j. &0) hc hdc a b +
     pde_jtrhess n (\i j. &0) gi d12 (\p q i j. &0) hc hdc a b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `&1`; `&1`; `\(i:num) (j:num). &0`; `\(i:num) (j:num). &0`;
                 `gi:num->num->real`; `d11:num->num->num->real`; `d12:num->num->num->real`;
                 `\(p:num) (q:num) (i:num) (j:num). &0`; `\(p:num) (q:num) (i:num) (j:num). &0`;
                 `hc:num->num->num->real`; `hdc:num->num->num->num->real`;
                 `a:num`; `b:num`] PDE_ML_JTRHESS_LIN) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RZERO; REAL_ADD_LID]);;

let PDE_ML_JT_D_CMUL = prove
 (`!n x (gi:num->num->real) d1 (hc:num->num->num->real) (hdc:num->num->num->num->real) a b.
     pde_jtrhess n (\i j. &0) gi (\c i j. x * d1 c i j) (\p q i j. &0) hc hdc a b =
     x * pde_jtrhess n (\i j. &0) gi d1 (\p q i j. &0) hc hdc a b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `x:real`; `&0`; `\(i:num) (j:num). &0`; `\(i:num) (j:num). &0`;
                 `gi:num->num->real`; `d1:num->num->num->real`; `d1:num->num->num->real`;
                 `\(p:num) (q:num) (i:num) (j:num). &0`; `\(p:num) (q:num) (i:num) (j:num). &0`;
                 `hc:num->num->num->real`; `hdc:num->num->num->num->real`;
                 `a:num`; `b:num`] PDE_ML_JTRHESS_LIN) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID]);;

let PDE_ML_JT_GD_SPLIT = prove
 (`!n g (gi:num->num->real) d1 (hc:num->num->num->real) (hdc:num->num->num->num->real) a b.
     pde_jtrhess n g gi d1 (\p q i j. &0) hc hdc a b =
     pde_jtrhess n g gi (\c i j. &0) (\p q i j. &0) hc hdc a b +
     pde_jtrhess n (\i j. &0) gi d1 (\p q i j. &0) hc hdc a b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `&1`; `&1`; `g:num->num->real`; `\(i:num) (j:num). &0`;
                 `gi:num->num->real`; `\(c:num) (i:num) (j:num). &0`; `d1:num->num->num->real`;
                 `\(p:num) (q:num) (i:num) (j:num). &0`; `\(p:num) (q:num) (i:num) (j:num). &0`;
                 `hc:num->num->num->real`; `hdc:num->num->num->num->real`;
                 `a:num`; `b:num`] PDE_ML_JTRHESS_LIN) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID; ETA_AX]);;

let PDE_ML_JT_D_SUM = prove
 (`!n m (gi:num->num->real) (d:num->num->num->num->real) (hc:num->num->num->real)
    (hdc:num->num->num->num->real) a b.
     pde_jtrhess n (\i j. &0) gi (\e i j. sum(1..m) (\c. d c e i j)) (\p q i j. &0)
                 hc hdc a b =
     sum(1..m) (\c. pde_jtrhess n (\i j. &0) gi (d c) (\p q i j. &0) hc hdc a b)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`] THEN
    MP_TAC(ISPECL [`n:num`; `&0`; `gi:num->num->real`; `\(e:num) (i:num) (j:num). &0`;
                   `hc:num->num->num->real`; `hdc:num->num->num->num->real`; `a:num`; `b:num`]
                  PDE_ML_JT_D_CMUL) THEN
    REWRITE_TAC[REAL_MUL_LZERO];
    REPEAT GEN_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
    MP_TAC(ISPECL [`n:num`; `gi:num->num->real`;
                   `\e i j. sum(1..m) (\c. (d:num->num->num->num->real) c e i j)`;
                   `(d:num->num->num->num->real) (SUC m)`; `hc:num->num->num->real`;
                   `hdc:num->num->num->num->real`; `a:num`; `b:num`] PDE_ML_JT_D_ADD) THEN
    REWRITE_TAC[ETA_AX]]);;

(* The coefficient matrices. *)

let pde_mlcc = new_definition
 `pde_mlcc (K:real^N->real^N^N) (H:real^N->real^N^N) (y:real^N) =
    (matrix (\w:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
       ((lambda a b. pde_jtrhess (dimindex(:N)) (\i j. (matrify w:real^N^N)$i$j) (pde_jgi K y)
                       (\c i j. &0) (\p q i j. &0) (pde_jhc H y) (pde_jhdc H y) a b):real^N^N)))
    :real^(N,N)finite_prod^(N,N)finite_prod`;;

let pde_mlbb = new_definition
 `pde_mlbb (K:real^N->real^N^N) (H:real^N->real^N^N) (y:real^N) (c:num) =
    (matrix (\w:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
       ((lambda a b. pde_jtrhess (dimindex(:N)) (\i j. &0) (pde_jgi K y)
                       (\e i j. if e = c then (matrify w:real^N^N)$i$j else &0)
                       (\p q i j. &0) (pde_jhc H y) (pde_jhdc H y) a b):real^N^N)))
    :real^(N,N)finite_prod^(N,N)finite_prod`;;

let PDE_ML_VECTORIZE_LAMBDA_LIN = prove
 (`!(FF:real^(N,N)finite_prod->num->num->real).
     (!w1 w2 a b. FF (w1 + w2) a b = FF w1 a b + FF w2 a b) /\
     (!x w a b. FF (x % w) a b = x * FF w a b)
     ==> linear (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                       ((lambda a b. FF w a b):real^N^N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN REWRITE_TAC[VECTORIZE_MATRIFY] THEN
  REWRITE_TAC[GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL; VECTORIZE_EQ] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  ASM_REWRITE_TAC[]);;

let PDE_MLCC_WORKS = prove
 (`!(K:real^N->real^N^N) (H:real^N->real^N^N) y w.
     pde_mlcc K H y ** w =
     (vectorize:real^N^N->real^(N,N)finite_prod)
       ((lambda a b. pde_jtrhess (dimindex(:N)) (\i j. (matrify w:real^N^N)$i$j) (pde_jgi K y)
                       (\c i j. &0) (\p q i j. &0) (pde_jhc H y) (pde_jhdc H y) a b):real^N^N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mlcc] THEN
  MP_TAC(ISPEC `\(w:real^(N,N)finite_prod) a b.
                  pde_jtrhess (dimindex(:N)) (\i j. (matrify w:real^N^N)$i$j)
                    (pde_jgi (K:real^N->real^N^N) y) (\c i j. &0) (\p q i j. &0)
                    (pde_jhc (H:real^N->real^N^N) y) (pde_jhdc H y) a b`
               PDE_ML_VECTORIZE_LAMBDA_LIN) THEN
  REWRITE_TAC[MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT;
              PDE_ML_JT_G_ADD; PDE_ML_JT_G_CMUL] THEN
  SIMP_TAC[MATRIX_WORKS]);;

let PDE_MLBB_WORKS = prove
 (`!(K:real^N->real^N^N) (H:real^N->real^N^N) y c w.
     pde_mlbb K H y c ** w =
     (vectorize:real^N^N->real^(N,N)finite_prod)
       ((lambda a b. pde_jtrhess (dimindex(:N)) (\i j. &0) (pde_jgi K y)
                       (\e i j. if e = c then (matrify w:real^N^N)$i$j else &0)
                       (\p q i j. &0) (pde_jhc H y) (pde_jhdc H y) a b):real^N^N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mlbb] THEN
  MP_TAC(ISPEC `\(w:real^(N,N)finite_prod) a b.
                  pde_jtrhess (dimindex(:N)) (\i j. &0) (pde_jgi (K:real^N->real^N^N) y)
                    (\e i j. if e = c then (matrify w:real^N^N)$i$j else &0) (\p q i j. &0)
                    (pde_jhc (H:real^N->real^N^N) y) (pde_jhdc H y) a b`
               PDE_ML_VECTORIZE_LAMBDA_LIN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; REAL_ADD_RID; REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_ARITH `(if p then a + b else &0) =
                            (if p then a else &0) + (if p then b else &0)`;
                REAL_ARITH `(if p then x * a else &0) = x * (if p then a else &0)`] THEN
    REWRITE_TAC[PDE_ML_JT_D_ADD; PDE_ML_JT_D_CMUL];
    SIMP_TAC[MATRIX_WORKS]]);;

(* ========================================================================= *)
(* The pde_lop0 form of tr_K Hess_H V:                                       *)
(*   vectorize(pde_ltrhess K H V y) =                                        *)
(*   pde_lop0 (transp o matrix_inv o K) (pde_mlbb K H) (pde_mlcc K H)        *)
(*            (vectorize o V) y                                              *)
(* for V smooth near y (PDE_ML_LOP0_FORM).                                   *)
(* ========================================================================= *)

let PDE_ML_JD1_OUT = prove
 (`!(V:real^N->real^N^N) y e i j.
     ((vectorize:real^N^N->real^(N,N)finite_prod) o V) differentiable (at y) /\
     ~(e IN 1..dimindex(:N))
     ==> pde_jd1 V y e i j = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jd1; mderiv] THEN
  SUBGOAL_THEN `basis e:real^N = vec 0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[BASIS_EQ_0]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP LINEAR_0) THEN
  SUBGOAL_THEN `matrify(vec 0:real^(N,N)finite_prod) = (mat 0:real^N^N)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`&0`; `vec 0:real^(N,N)finite_prod`] MATRIFY_CMUL) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; MATRIX_CMUL_LZERO];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `mat 0:real^N^N` MATRIX_CMUL_LZERO)] THEN
  REWRITE_TAC[MATRIX_CMUL_COMPONENT; REAL_MUL_LZERO]);;

let PDE_ML_JD1_SPLIT = prove
 (`!(V:real^N->real^N^N) y.
     ((vectorize:real^N^N->real^(N,N)finite_prod) o V) differentiable (at y)
     ==> pde_jd1 V y =
         (\e i j. sum(1..dimindex(:N)) (\c. if e = c then pde_jd1 V y c i j else &0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:num`; `i:num`; `j:num`] THEN
  SUBGOAL_THEN
   `!c. (if e = c then pde_jd1 (V:real^N->real^N^N) y c i j else &0) =
        (if c = e then pde_jd1 V y e i j else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_CASES_TAC `c:num = e` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_ML_JD1_OUT THEN ASM_REWRITE_TAC[]);;

let PDE_ML_VEC_EQ_MATRIFY = prove
 (`!(X:real^N^N) R. vectorize X = R <=> X = matrify R`,
  MESON_TAC[VECTORIZE_MATRIFY; MATRIFY_VECTORIZE]);;

let PDE_ML_MATRIFY_VSUM = prove
 (`!s (f:A->real^(N,N)finite_prod) a b.
     FINITE s
     ==> (matrify (vsum s f):real^N^N)$a$b = sum s (\i. (matrify (f i):real^N^N)$a$b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$a$b)`;
                 `f:A->real^(N,N)finite_prod`; `s:A->bool`] LINEAR_VSUM) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; o_DEF] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP; DROP_VSUM; o_DEF]);;

let PDE_ML_MATRIFY_ENTRY_CLAUSES = prove
 (`(!(x:real^(N,N)finite_prod) y a b.
      (matrify (x + y):real^N^N)$a$b = (matrify x:real^N^N)$a$b + (matrify y:real^N^N)$a$b) /\
   (!c (x:real^(N,N)finite_prod) a b.
      (matrify (c % x):real^N^N)$a$b = c * (matrify x:real^N^N)$a$b)`,
  REWRITE_TAC[MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT]);;

let PDE_ML_LOP0_FORM = prove
 (`!U (K:real^N->real^N^N) H (V:real^N->real^N^N) y.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H /\ y IN U
     ==> (vectorize:real^N^N->real^(N,N)finite_prod) (pde_ltrhess K H V y) =
         pde_lop0 (\y. transp(matrix_inv(K y))) (\y c. pde_mlbb K H y c)
                  (\y. pde_mlcc K H y) ((vectorize:real^N^N->real^(N,N)finite_prod) o V) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (V:real^N->real^N^N))
                differentiable (at (y:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PDE_ML_VEC_EQ_MATRIFY] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `V:real^N->real^N^N`; `y:real^N`; `a:num`; `b:num`] PDE_ML_TRHESS_JET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[PDE_JTRHESS_SPLIT] THEN ONCE_REWRITE_TAC[PDE_ML_JT_GD_SPLIT] THEN
  REWRITE_TAC[pde_lop0; PDE_ML_MATRIFY_ENTRY_CLAUSES] THEN
  SIMP_TAC[PDE_ML_MATRIFY_VSUM; FINITE_NUMSEG; PDE_ML_MATRIFY_ENTRY_CLAUSES] THEN
  REWRITE_TAC[PDE_MLBB_WORKS; PDE_MLCC_WORKS; MATRIFY_VECTORIZE] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[o_THM; MATRIFY_VECTORIZE] THEN
  SUBGOAL_THEN
   `!c. (\e i j. if e = c
                 then (matrify (partial_derivative c
                         ((vectorize:real^N^N->real^(N,N)finite_prod) o V) y):real^N^N)$i$j
                 else &0) =
        (\e i j. if e = c then pde_jd1 V y c i j else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[pde_jd1] THEN
    REWRITE_TAC[GSYM PDE_MDERIV_ENTRY_ITERATED; iterated_partial];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `dimindex(:N)`; `pde_jgi (K:real^N->real^N^N) y`;
                 `\c e i j. if e = c then pde_jd1 (V:real^N->real^N^N) y c i j else &0`;
                 `pde_jhc (H:real^N->real^N^N) y`; `pde_jhdc (H:real^N->real^N^N) y`;
                 `a:num`; `b:num`] PDE_ML_JT_D_SUM) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP PDE_ML_JD1_SPLIT th)]) THEN
  SUBGOAL_THEN `(\i j. ((V:real^N->real^N^N) y)$i$j) = pde_jg V y`
  SUBST1_TAC THENL [REWRITE_TAC[pde_jg]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = x' ==> (g + d) + x = x' + d + g`) THEN
  REWRITE_TAC[TRANSP_COMPONENT; pde_jgi; pde_jd2; iterated_partial] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* Naturality of tr_K Hess_H V under diffeomorphisms                         *)
(* (PDE_ML_LTRHESS_PULLBACK), through the bilinear form                      *)
(* a . (pde_ltrhess K H V y ** b) and the multilinearity of the 4-tensor     *)
(* nabla^2 V in its slots.                                                   *)
(* ========================================================================= *)

let PDE_ML_LOC4_TAC =
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[];;

let PDE_ML_SLOT4_STEP_TAC k v =
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC (subst [v,`vv:real^N`; k,`kk:num`]
   `(tp:(num->real^N)->real)
      (\j. if j = kk then vv
           else (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else d) j)`) THEN
  CONJ_TAC THENL [USE_THEN "LOC" MATCH_MP_TAC THEN PDE_ML_LOC4_TAC; ALL_TAC] THEN
  USE_THEN "SL" (fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP th
    (EQT_ELIM(NUM_REDUCE_CONV (subst [k,`kk:num`] `1 <= kk /\ kk <= 4`)))]) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN USE_THEN "LOC" MATCH_MP_TAC THEN PDE_ML_LOC4_TAC;;

let PDE_ML_SLOT4 = prove
 (`!(tp:(num->real^N)->real).
     (!u u'. (!m. 1 <= m /\ m <= 4 ==> u m = u' m) ==> tp u = tp u') /\
     (!i u. 1 <= i /\ i <= 4 ==> linear (\v. lift(tp (\j. if j = i then v else u j))))
     ==> !a b c d.
           tp (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else d) =
           sum(1..dimindex(:N))
             (\r. a$r * tp (\m. if m = 1 then basis r else if m = 2 then b
                                else if m = 3 then c else d)) /\
           tp (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else d) =
           sum(1..dimindex(:N))
             (\r. b$r * tp (\m. if m = 1 then a else if m = 2 then basis r
                                else if m = 3 then c else d)) /\
           tp (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else d) =
           sum(1..dimindex(:N))
             (\r. c$r * tp (\m. if m = 1 then a else if m = 2 then b
                                else if m = 3 then basis r else d)) /\
           tp (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else d) =
           sum(1..dimindex(:N))
             (\r. d$r * tp (\m. if m = 1 then a else if m = 2 then b
                                else if m = 3 then c else basis r))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LOC") ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!i (u:num->real^N) v. 1 <= i /\ i <= 4
        ==> (tp:(num->real^N)->real) (\j. if j = i then v else u j) =
            sum(1..dimindex(:N)) (\r. v$r * tp (\j. if j = i then basis r else u j))`
  (LABEL_TAC "SL") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SLOT_EXPAND THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [PDE_ML_SLOT4_STEP_TAC `1` `a:real^N`; PDE_ML_SLOT4_STEP_TAC `2` `b:real^N`;
    PDE_ML_SLOT4_STEP_TAC `3` `c:real^N`; PDE_ML_SLOT4_STEP_TAC `4` `d:real^N`]);;

(* The bilinear form of a matrix of traced 4-linear values. *)

let PDE_ML_DOT4 = prove
 (`!(tp:(num->real^N)->real) (A:real^N^N) a b.
     (!u u'. (!m. 1 <= m /\ m <= 4 ==> u m = u' m) ==> tp u = tp u') /\
     (!i u. 1 <= i /\ i <= 4 ==> linear (\v. lift(tp (\j. if j = i then v else u j))))
     ==> a dot (((lambda i j. sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q. A$p$q *
                    tp (\m. if m = 1 then basis i else if m = 2 then basis j
                            else if m = 3 then basis p else basis q)))):real^N^N) ** b) =
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q. A$p$q *
           tp (\m. if m = 1 then a else if m = 2 then b
                   else if m = 3 then basis p else basis q)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "S4" o MATCH_MP PDE_ML_SLOT4) THEN
  SUBGOAL_THEN
   `!p q. (tp:(num->real^N)->real)
            (\m. if m = 1 then a else if m = 2 then b else if m = 3 then basis p else basis q) =
          sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. a$i * b$j *
            tp (\m. if m = 1 then basis i else if m = 2 then basis j
                    else if m = 3 then basis p else basis q)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "S4" (fun th -> GEN_REWRITE_TAC LAND_CONV
      [CONJUNCT1(SPECL [`a:real^N`; `b:real^N`; `basis p:real^N`; `basis q:real^N`] th)]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "S4" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [CONJUNCT1(CONJUNCT2(SPECL [`basis i:real^N`; `b:real^N`; `basis p:real^N`;
                                  `basis q:real^N`] th))]) THEN
    REWRITE_TAC[GSYM SUM_LMUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  REMOVE_THEN "S4" (K ALL_TAC) THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. sum(1..dimindex(:N))
      (\p. sum(1..dimindex(:N)) (\q. (A:real^N^N)$p$q * ((a:real^N)$i * (b:real^N)$j *
         (tp:(num->real^N)->real) (\m. if m = 1 then basis i else if m = 2 then basis j
                 else if m = 3 then basis p else basis q))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; LAMBDA_BETA; dot] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [PDE_SUM4_SWAP] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL]]);;

let PDE_ML_T4_FIELD = prove
 (`!U (V:real^N->real^N^N) H y.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H /\ y IN U
     ==> (!u u'. (!m. 1 <= m /\ m <= 4 ==> u m = u' m)
                 ==> lnabla_iter 2 2 H (lmetric2 V) y u = lnabla_iter 2 2 H (lmetric2 V) y u') /\
         (!i u. 1 <= i /\ i <= 4
                ==> linear (\v. lift(lnabla_iter 2 2 H (lmetric2 V) y
                                       (\j. if j = i then v else u j))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `H:real^N->real^N^N`; `lmetric2 (V:real^N->real^N^N)`]
                LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[PDE_ML_LMETRIC2_FIELD] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `2`) THEN
  REWRITE_TAC[ARITH_RULE `2 + 2 = 4`; ltensor_field] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[]);;

let PDE_ML_LTRHESS_DOT = prove
 (`!U (K:real^N->real^N^N) H (V:real^N->real^N^N) y a b.
     open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     metric_field U H /\ y IN U
     ==> a dot (pde_ltrhess K H V y ** b) =
         sum(1..dimindex(:N))
           (\p. sum(1..dimindex(:N))
                  (\q. matrix_inv(K y)$p$q *
                       lnabla_iter 2 2 H (lmetric2 V) y
                         (\m. if m = 1 then a else if m = 2 then b
                              else if m = 3 then basis p else basis q)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_ltrhess] THEN MATCH_MP_TAC PDE_ML_DOT4 THEN
  MATCH_MP_TAC PDE_ML_T4_FIELD THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* Naturality. *)

let PDE_ML_TUPLE_MAP = prove
 (`!(f:real^N->real^N) a b c d.
     (\m. f (if m = 1 then a else if m = 2 then b else if m = 3 then c else d)) =
     (\m. if m = 1 then f a else if m = 2 then f b else if m = 3 then f c else f d)`,
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let PDE_ML_LMETRIC2_PULLBACK = prove
 (`!(phi:real^N->real^N) (V:real^N->real^N^N) z u.
     linear(frechet_derivative phi (at z))
     ==> lmetric2 (mpullback phi V) z u = ltpullback phi (lmetric2 V) z u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lmetric2; ltpullback; mpullback] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let PDE_ML_LTRHESS_PULLBACK = prove
 (`!(U:real^N->bool) U' (phi:real^N->real^N) phi' (K:real^N->real^N^N) H
    (V:real^N->real^N^N) y.
     diffeomorphism_on U' U phi phi' /\ metric_field U H /\
     smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o V) /\
     invertible(K(phi y)) /\ y IN U'
     ==> pde_ltrhess (mpullback phi K) (mpullback phi H) (mpullback phi V) y =
         transp(matrix(frechet_derivative phi (at y))) ** pde_ltrhess K H V (phi y) **
         matrix(frechet_derivative phi (at y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                 `phi':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `invertible(matrix(frechet_derivative (phi:real^N->real^N) (at y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_DIFFEO_JAC_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `phi':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U' (mpullback (phi:real^N->real^N) H)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `phi':real^N->real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U' ((vectorize:real^N^N->real^(N,N)finite_prod) o
                      mpullback (phi:real^N->real^N) V)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDM_MPULLBACK_SMOOTH THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_MATRIX_EQ_DOT THEN MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `mpullback (phi:real^N->real^N) K`;
                 `mpullback (phi:real^N->real^N) H`; `mpullback (phi:real^N->real^N) V`;
                 `y:real^N`; `a:real^N`; `b:real^N`] PDE_ML_LTRHESS_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `V:real^N->real^N^N`; `(phi:real^N->real^N) y`;
                 `matrix(frechet_derivative (phi:real^N->real^N) (at y)) ** a`;
                 `matrix(frechet_derivative (phi:real^N->real^N) (at y)) ** b`]
                PDE_ML_LTRHESS_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!u z. z IN U'
          ==> lnabla_iter 2 2 (mpullback (phi:real^N->real^N) H)
                (lmetric2 (mpullback phi (V:real^N->real^N^N))) z u =
              ltpullback phi (lnabla_iter 2 2 H (lmetric2 V)) z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `U':real^N->bool`; `phi:real^N->real^N`;
                   `phi':real^N->real^N`; `H:real^N->real^N^N`;
                   `lmetric2 (V:real^N->real^N^N)`;
                   `lmetric2 (mpullback (phi:real^N->real^N) (V:real^N->real^N^N))`]
                  LRG_LNABLA_ITER_PULLBACK) THEN
    ASM_SIMP_TAC[PDE_ML_LMETRIC2_FIELD] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ML_LMETRIC2_PULLBACK THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U':real^N->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`2`; `z:real^N`; `u:num->real^N`]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[ltpullback; PDE_ML_TUPLE_MAP] THEN
  SUBGOAL_THEN
   `!w. frechet_derivative (phi:real^N->real^N) (at y) w =
        matrix(frechet_derivative phi (at y)) ** w`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `V:real^N->real^N^N`; `H:real^N->real^N^N`;
                 `(phi:real^N->real^N) y`] PDE_ML_T4_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "S4" o MATCH_MP PDE_ML_SLOT4) THEN
  ABBREV_TAC `J = matrix(frechet_derivative (phi:real^N->real^N) (at y))` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
      matrix_inv(transp J ** (K:real^N->real^N^N) ((phi:real^N->real^N) y) ** J)$p$q *
      sum(1..dimindex(:N)) (\p'. sum(1..dimindex(:N)) (\q'. (J:real^N^N)$p'$p * J$q'$q *
        lnabla_iter 2 2 (H:real^N->real^N^N) (lmetric2 (V:real^N->real^N^N)) (phi y)
          (\m. if m = 1 then J ** a else if m = 2 then J ** b
               else if m = 3 then basis p' else basis q')))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REMOVE_THEN "S4" (K ALL_TAC) THEN
    MATCH_MP_TAC PDE_TRACE_CONGR_SUM THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  USE_THEN "S4" (fun th -> GEN_REWRITE_TAC LAND_CONV
    [CONJUNCT1(CONJUNCT2(CONJUNCT2(SPECL [`(J:real^N^N) ** a`; `(J:real^N^N) ** b`;
        `(J:real^N^N) ** basis p`; `(J:real^N^N) ** basis q`] th)))]) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p':num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "S4" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [CONJUNCT2(CONJUNCT2(CONJUNCT2(SPECL [`(J:real^N^N) ** a`; `(J:real^N^N) ** b`;
        `basis p':real^N`; `(J:real^N^N) ** basis q`] th)))]) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `q':num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REMOVE_THEN "S4" (K ALL_TAC) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DOT_BASIS] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Locality of pde_ltrhess, the chart form of pde_trhess                     *)
(* (PDE_ML_TRHESS_CHART) and of solutions of pde_mlin_sol                    *)
(* (PDE_ML_SOL_CHART_DERIV).                                                 *)
(* ========================================================================= *)

let PDE_ML_LTRHESS_LOCAL = prove
 (`!U (K:real^N->real^N^N) K' H H' V V' y.
     open U /\ y IN U /\ K y = K' y /\
     (!z. z IN U ==> H z = H' z /\ V z = V' z)
     ==> pde_ltrhess K H V y = pde_ltrhess K' H' V' y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_ltrhess] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`2`; `H:real^N->real^N^N`; `H':real^N->real^N^N`;
                 `lmetric2 (V:real^N->real^N^N)`; `lmetric2 (V':real^N->real^N^N)`;
                 `U:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ASM_SIMP_TAC[lmetric2]);;

(* The chart form of tr_K Hess_h v. *)

let PDE_ML_TRHESS_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (k:A->real^N^N) h (v:A->real^N^N) z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ riemannian_metric atlas k /\
     mfd_tensor2_smooth atlas v /\ z IN IMAGE (SND c) (FST c)
     ==> metric_local atlas c (pde_trhess atlas k h v) z =
         pde_ltrhess (metric_local atlas c k) (metric_local atlas c h)
                     (metric_local atlas c v) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. x IN FST (c:(A->bool)#(A->real^N)) /\ SND c x = (z:real^N) /\ chart_inv c z = x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  SUBGOAL_THEN
   `diffeomorphism_on (IMAGE (SND c) (FST c INTER FST c0))
                      (IMAGE (SND c0) (FST c INTER FST (c0:(A->bool)#(A->real^N))))
                      (chart_trans c c0) (chart_trans c0 c)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
                  CHART_TRANS_DIFFEO) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `!W:A->real^N^N z'. z' IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))
        ==> metric_local atlas c W z' =
            mpullback (chart_trans c c0) (metric_local atlas c0 W) z'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_METRIC_LOCAL_TRANS_C THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_trans c (c0:(A->bool)#(A->real^N)) z = SND c0 x` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `SND (c:(A->bool)#(A->real^N)) (x:A) = (z:real^N)`)) THEN
    MATCH_MP_TAC PDM_CHART_TRANS_AT_C THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (SND c0) (FST (c:(A->bool)#(A->real^N)) INTER FST c0) SUBSET
                IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `pde_ltrhess (mpullback (chart_trans c (c0:(A->bool)#(A->real^N)))
                             (metric_local atlas c0 (k:A->real^N^N)))
                          (mpullback (chart_trans c c0) (metric_local atlas c0 h))
                          (mpullback (chart_trans c c0) (metric_local atlas c0 v)) z` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_ML_LTRHESS_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST (c:(A->bool)#(A->real^N)) INTER FST c0)`;
                 `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`;
                 `chart_trans c (c0:(A->bool)#(A->real^N))`;
                 `chart_trans (c0:(A->bool)#(A->real^N)) c`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) k`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) h`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) v`; `z:real^N`]
                PDE_ML_LTRHESS_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[riemannian_metric];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_tensor2_smooth];
      MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`;
                     `metric_local atlas (c0:(A->bool)#(A->real^N)) k`;
                     `SND (c0:(A->bool)#(A->real^N)) x`] LRG_METRIC_INVERTIBLE) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]]];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN
  CONV_TAC(LAND_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pde_trhess; chart_jac]);;

(* Slices of time families. *)

let PDE_ML_UPTO_SLICE_OPEN = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K) t.
     open U /\ pde_upto a b U u /\ a <= t /\ t < b
     ==> smooth_map_on U (u t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FG:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y:real^N. (FG:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^N. (FG:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)) =
                FG o (\y. pastecart (lift t) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_SIMP_TAC[] THEN MAP_EVERY UNDISCH_TAC [`&0 < e`; `a <= t`; `t < b`] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let PDE_ML_TFAM_SLICE = prove
 (`!top atlas a b (v:real->A->real^N^N) t.
     smooth_manifold_atlas top atlas /\ pde_tfam_from atlas a b v /\ a <= t /\ t < b
     ==> mfd_tensor2_smooth atlas (v t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PDM_TFAM_FROM_UPTO; mfd_tensor2_smooth] THEN
  STRIP_TAC THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t) y)`;
                 `t:real`] PDE_ML_UPTO_SLICE_OPEN) THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[PDM_CHART_OPEN_C]);;

let PDE_ML_INDEX_SPLIT = prove
 (`!n k. 1 <= k /\ k <= n * n
         ==> 1 <= 1 + (k - 1) DIV n /\ 1 + (k - 1) DIV n <= n /\
             1 <= 1 + (k - 1) MOD n /\ 1 + (k - 1) MOD n <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k - 1`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k - 1) DIV n < n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* The equation of a solution in an arbitrary chart. *)

let PDE_ML_SOL_CHART_DERIV = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v0 (v:real->A->real^N^N) c t z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\
     a < t /\ t < b /\ z IN IMAGE (SND c) (FST c)
     ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (metric_local atlas c (v (drop s)) z)) has_vector_derivative
          vectorize(pde_ltrhess (metric_local atlas c (k t)) (metric_local atlas c h)
                                (metric_local atlas c (v t)) z +
                    metric_local atlas c (f t) z)) (at (lift t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_mlin_sol] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. x IN FST (c:(A->bool)#(A->real^N)) /\ SND c x = (z:real^N) /\
                      chart_inv c z = x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_AT_C]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_ltrhess (metric_local atlas c ((k:real->A->real^N^N) t)) (metric_local atlas c h)
                (metric_local atlas c ((v:real->A->real^N^N) t)) z =
    metric_local atlas c (pde_trhess atlas (k t) h (v t)) z`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_ML_TRHESS_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `J = matrix(chart_jac (c:(A->bool)#(A->real^N))
                                   (chart_at atlas (x:A)) x)` THEN
  SUBGOAL_THEN `!W:A->real^N^N. metric_local atlas (c:(A->bool)#(A->real^N)) W z =
                                transp J ** W x ** J`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[metric_local] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  ABBREV_TAC `a1 = 1 + (r - 1) DIV dimindex(:N)` THEN
  ABBREV_TAC `b1 = 1 + (r - 1) MOD dimindex(:N)` THEN
  SUBGOAL_THEN
   `((\r. (transp (J:real^N^N) ** (v:real->A->real^N^N) r x ** J)$a1$b1) has_real_derivative
     ((transp J ** pde_trhess atlas ((k:real->A->real^N^N) t) h (v t) x ** J +
       transp J ** (f:real->A->real^N^N) t x ** J)$a1$b1)) (atreal t)`
  MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF]] THEN
  SUBGOAL_THEN `1 <= a1 /\ a1 <= dimindex(:N) /\ 1 <= b1 /\ b1 <= dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`dimindex(:N)`; `r:num`] PDE_ML_INDEX_SPLIT) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ADD_COMPONENT; PDE_MATRIX_TRIPLE_ENTRY; GSYM SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[REAL_ARITH `a * x * b + a * y * b = a * (x + y) * b`] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  REWRITE_TAC[GSYM MATRIX_ADD_COMPONENT] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The chart coefficients of the operator (pde_mlaa, pde_mlbt, pde_mlct:     *)
(* time-dependent coefficient fields in a chart) and the chart equation of a *)
(* solution in pde_lop form (PDE_ML_SOL_CHART_LOP), the bridge to the torus  *)
(* theory.                                                                   *)
(* ========================================================================= *)

let pde_mlaa = new_definition
 `pde_mlaa (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
           (k:real->A->real^N^N) (t:real) (y:real^N) =
    transp(matrix_inv(metric_local atlas c (k t) y))`;;

let pde_mlbt = new_definition
 `pde_mlbt (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
           (k:real->A->real^N^N) (h:A->real^N^N) (t:real) (y:real^N) (i:num) =
    pde_mlbb (metric_local atlas c (k t)) (metric_local atlas c h) y i`;;

let pde_mlct = new_definition
 `pde_mlct (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
           (k:real->A->real^N^N) (h:A->real^N^N) (t:real) (y:real^N) =
    pde_mlcc (metric_local atlas c (k t)) (metric_local atlas c h) y`;;

let PDE_ML_COEFF_FUN = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) c (k:real->A->real^N^N) h t.
     pde_mlaa atlas c k t = (\y. transp(matrix_inv(metric_local atlas c (k t) y))) /\
     pde_mlbt atlas c k h t =
       (\y i. pde_mlbb (metric_local atlas c (k t)) (metric_local atlas c h) y i) /\
     pde_mlct atlas c k h t =
       (\y. pde_mlcc (metric_local atlas c (k t)) (metric_local atlas c h) y)`,
  REWRITE_TAC[FUN_EQ_THM; pde_mlaa; pde_mlbt; pde_mlct]);;

let PDE_ML_SOL_CHART_LOP = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v0 (v:real->A->real^N^N) c t z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\
     a < t /\ t < b /\ z IN IMAGE (SND c) (FST c)
     ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (metric_local atlas c (v (drop s)) z)) has_vector_derivative
          pde_lop (pde_mlaa atlas c k) (pde_mlbt atlas c k h) (pde_mlct atlas c k h)
                  (\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas c (v t) y)) t z +
          vectorize(metric_local atlas c (f t) z)) (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                 `v0:A->real^N^N`; `v:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `t:real`; `z:real^N`] PDE_ML_SOL_CHART_DERIV) THEN
  ASM_REWRITE_TAC[VECTORIZE_ADD] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PDE_LOP_LOP0] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((k:real->A->real^N^N) t)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t)`;
                 `z:real^N`] PDE_ML_LOP0_FORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PDM_CHART_OPEN_C];
      SUBGOAL_THEN `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t)` MP_TAC THENL
       [MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[pde_mlin_sol];
        REWRITE_TAC[mfd_tensor2_smooth] THEN ASM_MESON_TAC[]];
      ASM_MESON_TAC[riemannian_metric]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PDE_ML_COEFF_FUN; o_DEF; ETA_AX]);;

(* ========================================================================= *)
(* Solutions from chart equations (PDE_ML_SOL_FROM_CHART): a time family     *)
(* that is smooth up to a, takes the initial value, and satisfies the chart  *)
(* equation in some chart around every point solves pde_mlin_sol.            *)
(* ========================================================================= *)

let PDE_ML_UNCONGR = prove
 (`!(J:real^N^N) (M:real^N^N). invertible J
     ==> M = transp(matrix_inv J) ** (transp J ** M ** J) ** matrix_inv J`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_RID]);;

let PDE_ML_VEC_COMPONENT = prove
 (`!(M:real^N^N) p q.
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> (vectorize M)$((p - 1) * dimindex(:N) + q) = M$p$q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vectorize(M:real^N^N)`; `p:num`; `q:num`] MATRIFY_COMPONENT) THEN
  ASM_REWRITE_TAC[MATRIFY_VECTORIZE] THEN SIMP_TAC[]);;

let PDE_ML_VEC_INDEX_RANGE = prove
 (`!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
         ==> 1 <= (p - 1) * dimindex(:N) + q /\
             (p - 1) * dimindex(:N) + q <= dimindex(:(N,N)finite_prod)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(p - 1) * dimindex(:N) + dimindex(:N)` THEN
  ASM_REWRITE_TAC[LE_ADD_LCANCEL] THEN
  SUBGOAL_THEN `(p - 1) * dimindex(:N) + dimindex(:N) = p * dimindex(:N)` SUBST1_TAC THENL
   [SUBGOAL_THEN `p = (p - 1) + 1` (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES]];
    ASM_REWRITE_TAC[LE_MULT_RCANCEL]]);;

let PDE_ML_CONGR_DERIV = prove
 (`!(G:real->real^N^N) (TT:real^N^N) (P:real^N^N) i j t.
     ((\s. (vectorize:real^N^N->real^(N,N)finite_prod) (G (drop s))) has_vector_derivative
      vectorize TT) (at (lift t)) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> ((\s. (transp P ** G s ** P)$i$j) has_real_derivative
          (transp P ** TT ** P)$i$j) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> ((\s. ((G:real->real^N^N) s)$p$q) has_real_derivative (TT:real^N^N)$p$q)
              (atreal t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((G:real->real^N^N) (drop s))`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) TT`; `lift t`;
                   `(p - 1) * dimindex(:N) + q`] HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT) THEN
    ASM_SIMP_TAC[PDE_ML_VEC_INDEX_RANGE; PDE_ML_VEC_COMPONENT] THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[PDE_MATRIX_TRIPLE_ENTRY] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN ASM_SIMP_TAC[]);;

let PDE_ML_SOL_FROM_CHART = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v0 (v:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_tfam_from atlas a b v /\ (!x. x IN topspace top ==> v a x = v0 x) /\
     (!x. x IN topspace top
          ==> ?c. c IN atlas /\ x IN FST c /\
                  !t. a < t /\ t < b
                      ==> ((\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                                  (metric_local atlas c (v (drop s)) (SND c x)))
                           has_vector_derivative
                           vectorize(pde_ltrhess (metric_local atlas c (k t))
                                                 (metric_local atlas c h)
                                                 (metric_local atlas c (v t)) (SND c x) +
                                     metric_local atlas c (f t) (SND c x))) (at (lift t)))
     ==> pde_mlin_sol (top,atlas) a b k h f v0 v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[pde_mlin_sol] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `z = SND (c:(A->bool)#(A->real^N)) (x:A)` THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z = (x:A)` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `J = matrix(chart_jac (c:(A->bool)#(A->real^N)) c0 (x:A))` THEN
  SUBGOAL_THEN `!W:A->real^N^N. metric_local atlas (c:(A->bool)#(A->real^N)) W z =
                                transp (J:real^N^N) ** W x ** J`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[metric_local] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(J:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[chart_jac] THEN
    MATCH_MP_TAC PDE_DIFFEO_JAC_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST (c:(A->bool)#(A->real^N)) INTER FST c0)`;
      `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`;
      `chart_trans (c0:(A->bool)#(A->real^N)) (c:(A->bool)#(A->real^N))`] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
                    CHART_TRANS_DIFFEO) THEN
      ASM_REWRITE_TAC[PAIR];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_ltrhess (metric_local atlas c ((k:real->A->real^N^N) t)) (metric_local atlas c h)
                (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t)) z =
    metric_local atlas c (pde_trhess atlas (k t) h (v t)) z`
  SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_ML_TRHESS_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      EXPAND_TAC "z" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Ji = matrix_inv(J:real^N^N)` THEN
  SUBGOAL_THEN
   `!s. (v:real->A->real^N^N) s x =
        transp (Ji:real^N^N) ** metric_local atlas (c:(A->bool)#(A->real^N)) (v s) z ** Ji`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Ji" THEN
    MATCH_MP_TAC PDE_ML_UNCONGR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_trhess atlas ((k:real->A->real^N^N) t) h ((v:real->A->real^N^N) t) x + f t x =
    transp (Ji:real^N^N) **
                 (metric_local atlas (c:(A->bool)#(A->real^N)) (pde_trhess atlas (k t) h (v t)) z +
                  metric_local atlas c (f t) z) ** Ji`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM MATRIX_ADD_LDISTRIB; GSYM MATRIX_ADD_RDISTRIB] THEN
    EXPAND_TAC "Ji" THEN MATCH_MP_TAC PDE_ML_UNCONGR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. (v:real->A->real^N^N) s x$i$j) =
    (\s. (transp (Ji:real^N^N) ** metric_local atlas (c:(A->bool)#(A->real^N)) (v s) z ** Ji)$i$j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) r) z`;
                 `metric_local atlas (c:(A->bool)#(A->real^N))
                    (pde_trhess atlas ((k:real->A->real^N^N) t) h ((v:real->A->real^N^N) t)) z +
                  metric_local atlas c ((f:real->A->real^N^N) t) z`;
                 `Ji:real^N^N`; `i:num`; `j:num`; `t:real`] PDE_ML_CONGR_DERIV) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

